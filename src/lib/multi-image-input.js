import React, { useState, useRef, useEffect } from 'react';
import PropTypes from 'prop-types';
import ReactCrop from 'react-image-crop';
import { ThemeProvider } from 'styled-components';
import ImageIcon from './components/ImageIcon';
import ImageOverlay from './components/ImageOverlay';
import ImageBox from './components/ImageBox';
import ImageInput from './components/ImageInput';
import { Button, DeleteImageButton } from './components/Button';
import Image from './components/Image';
import Text from './components/Text';
import theme, { darkTheme, lightTheme } from './theme';
import 'react-image-crop/dist/ReactCrop.css';

export default function MultiImageInput({
  images: files,
  setImages: setFiles,
  cropConfig: { crop: userDefinedCrop },
  max,
  allowCrop,
  ...props
}) {
  const [numberOfImages, setNumberOfImages] = useState(1);

  const [fileUploadRefs, setFileUploadRefs] = useState({});

  const [imagePreviews, setImagePreviews] = useState({});

  const [currentImage, setCurrentImage] = useState(null);

  const currentFile = useRef(null);

  const currentFileInputIndex = useRef(null);

  const [crop, setCrop] = useState(userDefinedCrop);

  let userTheme;

  if (typeof props.theme === 'string') {
    userTheme = props.theme === 'light' ? lightTheme : darkTheme;
  } else if (typeof props.theme === 'object') {
    userTheme = props.theme;
  }

  useEffect(() => {
    const fileUploadRefsCopy = {};

    Array(numberOfImages)
      .fill()
      .forEach((_, index) => {
        fileUploadRefsCopy[index] = React.createRef();
      });

    setFileUploadRefs(fileUploadRefsCopy);
  }, [numberOfImages]);

  useEffect(() => {
    if (numberOfImages < max && files[numberOfImages - 1]) {
      setNumberOfImages(n => n + 1);
    }
  }, [files, max, numberOfImages]);

  const handleFileChange = (e, index) => {
    e.preventDefault();

    currentFileInputIndex.current = index;

    let reader = new FileReader();

    const file = e.target.files[0];

    reader.onloadend = () => {
      setCurrentImage(reader.result);
    };

    if (file) {
      reader.readAsDataURL(file);
    }
  };

  const onCropComplete = crop => {
    makeClientCrop(crop);
  };

  const onImageLoaded = image => {
    currentFile.current = image;
  };

  const makeClientCrop = crop => {
    const imageRef = currentFile.current;
    if (imageRef && imageRef.width && imageRef.height) {
      const base64Image = getCroppedImage(imageRef, crop);

      setImagePreviews({
        ...imagePreviews,
        [currentFileInputIndex.current]: base64Image
      });

      setFiles({ ...files, [currentFileInputIndex.current]: base64Image });
    }
  };

  const getCroppedImage = (image, crop) => {
    const canvas = document.createElement('canvas');

    const scaleX = image.naturalWidth / image.width;

    const scaleY = image.naturalHeight / image.height;

    canvas.width = crop.width;

    canvas.height = crop.height;

    const ctx = canvas.getContext('2d');

    ctx.drawImage(
      image,
      crop.x * scaleX,
      crop.y * scaleY,
      crop.width * scaleY,
      crop.height * scaleY,
      0,
      0,
      crop.width,
      crop.height
    );

    const base64Image = canvas.toDataURL('image/jpeg');

    return base64Image;
  };

  const exitCrop = e => {
    if (e) {
      e.preventDefault();
    }
    setCurrentImage(null);
    currentFile.current = null;
    currentFileInputIndex.current = null;
  };

  const removeImage = (e, index) => {
    fileUploadRefs[index].current.value = '';

    delete files[index];
    delete imagePreviews[index];

    const reIndexedFiles = {};
    const reIndexedPreviews = {};

    for (let i = index - 1; i >= 0; i--) {
      reIndexedFiles[i] = files[i];
      reIndexedPreviews[i] = imagePreviews[i];
    }

    for (let i = index; i < numberOfImages - 1; i++) {
      reIndexedFiles[i] = files[i + 1];
      reIndexedPreviews[i] = imagePreviews[i + 1];
    }

    setImagePreviews(reIndexedPreviews);
    setFiles(reIndexedFiles);
    setNumberOfImages(n => n - 1);

    exitCrop();

    e.stopPropagation();
    return;
  };

  return (
    <ThemeProvider theme={{ ...theme, ...userTheme }}>
      <ImageBox>
        {Array(numberOfImages)
          .fill()
          .map((_, index) => (
            <ImageInput key={index}>
              {imagePreviews[index] ? (
                <>
                  <DeleteImageButton
                    onClick={e => removeImage(e, index)}
                    type='button'
                  />
                  <ImageOverlay>
                    <Image
                      src={imagePreviews[index]}
                      onClick={() => fileUploadRefs[index].current.click()}
                    />
                  </ImageOverlay>
                </>
              ) : (
                <div
                  onClick={() => fileUploadRefs[index].current.click()}
                  style={{ cursor: 'pointer' }}
                >
                  <ImageIcon
                    style={{ marginBottom: '0.5rem' }}
                    width={58}
                    height={46}
                  />
                  <Text
                    fontSize='small'
                    color='outlineColor'
                    style={{ display: 'block' }}
                  >
                    ADD IMAGE
                  </Text>
                </div>
              )}
              <input
                type='file'
                onChange={e => handleFileChange(e, index)}
                ref={fileUploadRefs[index]}
                style={{ visibility: 'hidden' }}
                accept='image/*'
              />
            </ImageInput>
          ))}
      </ImageBox>
      {allowCrop && currentImage && (
        <>
          <ReactCrop
            src={currentImage}
            crop={crop}
            onChange={setCrop}
            onImageLoaded={onImageLoaded}
            onComplete={onCropComplete}
            {...props.cropConfig}
          />
          <Button
            type='button'
            onClick={exitCrop}
            size='small'
            style={{ marginTop: '1rem', display: 'block' }}
          >
            Crop
          </Button>
        </>
      )}
    </ThemeProvider>
  );
}

MultiImageInput.defaultProps = {
  max: 3,
  theme: 'dark',
  allowCrop: true,
  cropConfig: {
    maxCropWidth: 800,
    minCropHeight: 300,
    crop: {},
    ruleOfThirds: true
  }
};

MultiImageInput.propTypes = {
  images: PropTypes.object.isRequired,
  setImages: PropTypes.func.isRequired,
  allowCrop: PropTypes.bool,
  max: PropTypes.number,
  theme: PropTypes.oneOfType([PropTypes.object, PropTypes.string]),
  cropConfig: PropTypes.object
};
